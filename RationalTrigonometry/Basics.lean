/-
Copyright (c) 2026 Forest Belton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Forest Belton
-/
import RationalTrigonometry.Line

/-!
# Rational trigonometry: quadrance, spread, and the laws of a triangle

This file introduces the two fundamental quantities of rational trigonometry —
`quad` (quadrance, the squared separation of two points) and `spread` (the
rational replacement for the angle between two lines) — and states the main laws
for a triple of points: the triple quad formula, Pythagoras, the spread law, the
cross law, and the triple spread formula.

A `Point3` is three pairwise-apart points; a `Triangle` refines it with a
non-collinearity constraint.
-/

variable {K : Type*} [Field K]

def quad (p q : Point K) : K := (q.x - p.x) ^ 2 + (q.y - p.y) ^ 2

def spread (l m : Line K) : K :=
  ((l.a * m.b - m.a * l.b) ^ 2) / ((l.a ^ 2 + l.b ^ 2) * (m.a ^ 2 + m.b ^ 2))

structure Point3 (K : Type*) [Field K] where
  a₁ : Point K
  a₂ : Point K
  a₃ : Point K
  apart₁ : Apart a₁ a₂
  apart₂ : Apart a₁ a₃
  apart₃ : Apart a₂ a₃

structure Triangle (K : Type*) [Field K] extends Point3 K where
  not_collinear : ¬ Collinear toPoint3.a₁ toPoint3.a₂ toPoint3.a₃

class IsPoint3 (T : Type*) (K : outParam Type*) [Field K] where
  point3 : T → Point3 K

instance : IsPoint3 (Point3 K) K := ⟨id⟩
instance : IsPoint3 (Triangle K) K := ⟨Triangle.toPoint3⟩

def Q₁ {T : Type*} [IsPoint3 T K] (t : T) : K :=
  let p := IsPoint3.point3 t; quad p.a₂ p.a₃

def Q₂ {T : Type*} [IsPoint3 T K] (t : T) : K :=
  let p := IsPoint3.point3 t; quad p.a₁ p.a₃

def Q₃ {T : Type*} [IsPoint3 T K] (t : T) : K :=
  let p := IsPoint3.point3 t; quad p.a₁ p.a₂

def s₁ {T : Type*} [IsPoint3 T K] (t : T) : K :=
  let p := IsPoint3.point3 t
  spread (line_between p.a₁ p.a₂ p.apart₁) (line_between p.a₁ p.a₃ p.apart₂)

def s₂ {T : Type*} [IsPoint3 T K] (t : T) : K :=
  let p := IsPoint3.point3 t
  spread (line_between p.a₁ p.a₂ p.apart₁) (line_between p.a₂ p.a₃ p.apart₃)

def s₃ {T : Type*} [IsPoint3 T K] (t : T) : K :=
  let p := IsPoint3.point3 t
  spread (line_between p.a₁ p.a₃ p.apart₂) (line_between p.a₂ p.a₃ p.apart₃)

theorem triple_quad (t : Point3 K)
: Collinear t.a₁ t.a₂ t.a₃
↔ (Q₁ t + Q₂ t + Q₃ t) ^ 2 = 2 * (Q₁ t ^ 2 + Q₂ t ^ 2 + Q₃ t ^ 2)
:= sorry

theorem pythag (t : Point3 K)
: Q₁ t + Q₂ t = Q₃ t
↔ Perpendicular (line_between t.a₁ t.a₃ t.apart₂) (line_between t.a₂ t.a₃ t.apart₃)
:= sorry

theorem spread_law (t : Triangle K)
: Q₁ t ≠ 0 ∧ Q₂ t ≠ 0 ∧ Q₃ t ≠ 0
→ s₁ t / Q₁ t = s₂ t / Q₂ t ∧ s₁ t / Q₁ t = s₃ t / Q₃ t
:= sorry

def c₃ {T : Type*} [IsPoint3 T K] (t : T) : K := 1 - s₃ t

theorem cross_law (t : Triangle K)
: (Q₁ t + Q₂ t - Q₃ t) ^ 2 = 4 * Q₁ t * Q₂ t * c₃ t
:= sorry

theorem triple_spread (t : Triangle K)
: (s₁ t + s₂ t + s₃ t) ^ 2
  = 2 * (s₁ t ^ 2 + s₂ t ^ 2 + s₃ t ^2) + 4 * s₁ t * s₂ t * s₃ t
:= sorry
