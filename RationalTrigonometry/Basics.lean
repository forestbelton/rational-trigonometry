/-
Copyright (c) 2026 Forest Belton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Forest Belton
-/
import RationalTrigonometry.Line
import PolyrithLocal.Polyrith

/-!
# Rational trigonometry: quadrance, spread, and the laws of a triangle

This file introduces the two fundamental quantities of rational trigonometry —
`quad` (quadrance, the squared separation of two points) and `spread` (the
rational replacement for the angle between two lines) — with their basic
properties (`quad_comm`, `spread_comm`, and `spread_para` / `spread_perp`, giving
spread `0` for parallel and `1` for perpendicular lines), and states the main laws
for a triple of points: the triple quad formula, Pythagoras, the spread law, the
cross law, and the triple spread formula.

A `Point3` is three pairwise-apart points; `Triangle p` is the predicate that they
are non-collinear.

The spread-based laws (`spread_law` and `triple_spread`) require the quadrances to
be nonzero: a spread divides by the quadrances of its arms, so a vanishing
quadrance leaves it undefined. Over a general field `Apart` does not imply
`quad ≠ 0` (see `RationalTrigonometry.Line.Null`), so this is carried explicitly.
The condition factors through `Neg1NotSquare K` (no element squares to `-1`):
`quad_ne_zero` lifts it to a single quadrance and `qn_ne_zero` bundles all three
into the `Qᵢ ≠ 0` shape those laws expect, while `lin_order_neg1_not_sq` supplies
`Neg1NotSquare` automatically over an ordered field.
-/

variable {K : Type*} [Field K]

def quad (p q : Point K) : K := (q.x - p.x) ^ 2 + (q.y - p.y) ^ 2

def Neg1NotSquare (K : Type*) [Field K] : Prop := ∀ x : K, x * x ≠ -1

theorem lin_order_neg1_not_sq [LinearOrder K] [IsOrderedRing K] : Neg1NotSquare K := by
  intro x
  have h : x * x > -1 := by
    calc x * x
      _ = x ^ 2 := by rw [← sq x]
      _ ≥ 0     := sq_nonneg x
      _ > -1    := neg_one_lt_zero
  exact Ne.symm (ne_of_lt h)

theorem quad_comm {p q : Point K} : quad p q = quad q p
:= by
  unfold quad
  ring

theorem quad_ne_zero {p q : Point K} : Neg1NotSquare K → Apart p q → quad p q ≠ 0 := by
  simp only [Neg1NotSquare, Apart, quad]
  intro zns apq qp0
  rcases apq with xne | yne
  · have h := sub_ne_zero.mpr xne
    apply zns ((q.y - p.y) / (p.x - q.x))
    field_simp
    linear_combination qp0
  · have h := sub_ne_zero.mpr yne
    apply zns ((q.x - p.x) / (p.y - q.y))
    field_simp
    linear_combination qp0

def spread (l m : Line K) : K :=
  ((l.a * m.b - m.a * l.b) ^ 2) / ((l.a ^ 2 + l.b ^ 2) * (m.a ^ 2 + m.b ^ 2))

theorem spread_comm {l m : Line K} : spread l m = spread m l
:= by
  unfold spread
  ring

theorem spread_para {l m : Line K}
: Parallel l m
→ spread l m = 0
:= by
  unfold Parallel spread
  intro plm
  rw [plm]
  ring

theorem spread_perp {l m : Line K}
: Perpendicular l m
→ spread l m = 1
:= by
  unfold Perpendicular spread
  intro plm
  sorry

structure Point3 (K : Type*) [Field K] where
  a₁ : Point K
  a₂ : Point K
  a₃ : Point K
  apart₁ : Apart a₁ a₂
  apart₂ : Apart a₁ a₃
  apart₃ : Apart a₂ a₃

def Triangle (p : Point3 K) : Prop
:= ¬ Collinear p.a₁ p.a₂ p.a₃

def Q₁ (p : Point3 K) : K := quad p.a₂ p.a₃

def Q₂ (p : Point3 K) : K := quad p.a₁ p.a₃

def Q₃ (p : Point3 K) : K := quad p.a₁ p.a₂

theorem quads_ne_zero (p : Point3 K)
: Neg1NotSquare K
→ Q₁ p ≠ 0 ∧ Q₂ p ≠ 0 ∧ Q₃ p ≠ 0
:= by
  intro nns
  simp only [Q₁, Q₂, Q₃]
  exact ⟨
    quad_ne_zero nns p.apart₃,
    quad_ne_zero nns p.apart₂,
    quad_ne_zero nns p.apart₁,
  ⟩

def s₁ (p : Point3 K) : K :=
  spread (line_between p.a₁ p.a₂ p.apart₁) (line_between p.a₁ p.a₃ p.apart₂)

def s₂ (p : Point3 K) : K :=
  spread (line_between p.a₁ p.a₂ p.apart₁) (line_between p.a₂ p.a₃ p.apart₃)

def s₃ (p : Point3 K) : K :=
  spread (line_between p.a₁ p.a₃ p.apart₂) (line_between p.a₂ p.a₃ p.apart₃)

theorem triple_quad (t : Point3 K)
: Collinear t.a₁ t.a₂ t.a₃
↔ (Q₁ t + Q₂ t + Q₃ t) ^ 2 = 2 * (Q₁ t ^ 2 + Q₂ t ^ 2 + Q₃ t ^ 2)
:= by
  simp only [Collinear, Q₁, Q₂, Q₃, quad, HasPoint]
  constructor
  · intro ⟨l, p₁, p₂, p₃⟩
    sorry
  · sorry

theorem pythag (t : Point3 K) (h : Triangle t)
: Q₁ t + Q₂ t = Q₃ t
↔ Perpendicular (line_between t.a₁ t.a₃ t.apart₂) (line_between t.a₂ t.a₃ t.apart₃)
:= sorry

theorem spread_law (t : Point3 K)
: Q₁ t ≠ 0 ∧ Q₂ t ≠ 0 ∧ Q₃ t ≠ 0
→ s₁ t / Q₁ t = s₂ t / Q₂ t ∧ s₁ t / Q₁ t = s₃ t / Q₃ t
:= by
  intro ⟨q1n0, q2n0, q3n0⟩
  sorry

def c₃ (t : Point3 K) : K := 1 - s₃ t

theorem cross_law (t : Point3 K)
: (Q₁ t + Q₂ t - Q₃ t) ^ 2 = 4 * Q₁ t * Q₂ t * c₃ t
:= by
  sorry

theorem triple_spread (t : Point3 K)
: Q₁ t ≠ 0 ∧ Q₂ t ≠ 0 ∧ Q₃ t ≠ 0
→ (s₁ t + s₂ t + s₃ t) ^ 2
  = 2 * (s₁ t ^ 2 + s₂ t ^ 2 + s₃ t ^2) + 4 * s₁ t * s₂ t * s₃ t
:= by
  intro ⟨hQ₁, hQ₂, hQ₃⟩
  -- a line's `a² + b²` is exactly the quadrance of its endpoints, so the spread
  -- denominators are nonzero precisely when the quadrances are
  have key : ∀ (a b : Point K) (h : Apart a b), quad a b ≠ 0 →
      (line_between a b h).a ^ 2 + (line_between a b h).b ^ 2 ≠ 0 := by
    intro a b h hq
    rwa [show (line_between a b h).a ^ 2 + (line_between a b h).b ^ 2 = quad a b from by
      simp only [line_between, quad]; ring]
  have h12 := key _ _ t.apart₁ hQ₃
  have h13 := key _ _ t.apart₂ hQ₂
  have h23 := key _ _ t.apart₃ hQ₁
  simp only [s₁, s₂, s₃, spread]
  field_simp [h12, h13, h23]
  simp only [line_between]
  ring
