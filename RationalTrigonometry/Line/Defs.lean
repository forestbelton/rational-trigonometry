/-
Copyright (c) 2026 Forest Belton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Forest Belton
-/
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs

/-!
# Lines and points: basic definitions

Core structures for the affine plane over a field `K`: lines (`Line`), lines
through the origin (`Line0`), and points (`Point`), together with incidence
(`HasPoint`) and the `Apart` relation on points.
-/

variable {K : Type*} [Field K]

@[ext]
structure Line0 (K : Type*) [Field K] where
  a : K
  b : K
  ab_ne_zero : a ≠ 0 ∨ b ≠ 0

@[ext]
structure Line (K : Type*) [Field K] where
  a : K
  b : K
  c : K
  ab_ne_zero : a ≠ 0 ∨ b ≠ 0

def line0 (l : Line0 K) : Line K :=
  { a := l.a, b := l.b, c := 0, ab_ne_zero := l.ab_ne_zero }

theorem line0_inj (l m : Line0 K) : l = m ↔ line0 l = line0 m
:= by
  constructor
  · intro h
    rw [h]
  · intro h
    unfold line0 at h
    simp only [Line.mk.injEq, and_true] at h
    exact Line0.ext h.left h.right

@[ext]
structure Point (K : Type*) [Field K] where
  x : K
  y : K

def HasPoint (l : Line K) (p : Point K) : Prop :=
  l.a * p.x + l.b * p.y + l.c = 0

def Apart (a b : Point K) : Prop :=
  a.x ≠ b.x ∨ a.y ≠ b.y

def origin : Point K := ⟨0, 0⟩
