/-
Copyright (c) 2026 Forest Belton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Forest Belton
-/
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic.Ring
import RationalTrigonometry.Line.Point

/-!
# Lines and points: basic definitions

Core structures for the affine plane over a field `K`: lines (`Line`), lines
through the origin (`Line0`), and points (`Point`), together with incidence
(`HasPoint`) and the `Apart` relation on points.
-/

variable {K : Type*} [Field K]

@[ext]
structure Line (K : Type*) [Field K] where
  a : K
  b : K
  c : K
  ab_ne_zero : a ≠ 0 ∨ b ≠ 0

def Central (l : Line K) : Prop := l.c = 0

def HasPoint (l : Line K) (p : Point K) : Prop :=
  l.a * p.x + l.b * p.y + l.c = 0

def Collinear (a b c : Point K) : Prop :=
  ∃ l : Line K, HasPoint l a ∧ HasPoint l b ∧ HasPoint l c
