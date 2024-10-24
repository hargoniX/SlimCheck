/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import SlimCheck

/-!
Demonstrate that SlimCheck can handle the basic types from core:
- Sum
- Sigma
- Unit
- Prod
- Bool
- Nat
- Fin
- UIntX
- BitVec
- Char
- Option
- List
- String
- Array
-/


/-- error: Found a counter-example! -/
#guard_msgs in
example (a b : Sum Nat Nat) : a = b := by
  slim_check (config := {quiet := true})

/-- error: Found a counter-example! -/
#guard_msgs in
example (a b : Σ n : Nat, Nat) : a.fst = b.snd := by
  slim_check (config := {quiet := true})

/-- error: Found a counter-example! -/
#guard_msgs in
example (a b : Unit) : a ≠ b := by
  slim_check (config := {quiet := true})

/-- error: Found a counter-example! -/
#guard_msgs in
example (x y : Nat × Unit) : x = y := by
  slim_check (config := {quiet := true})

/-- error: Found a counter-example! -/
#guard_msgs in
example (a b : Bool) : a = b :=  by
  slim_check (config := {quiet := true})

/-- error: Found a counter-example! -/
#guard_msgs in
example (a b c : Nat) : a + (b - c) = (a + b) - c := by
  slim_check (config := {quiet := true})

/-- error: Found a counter-example! -/
#guard_msgs in
example (a : Fin (n + 1)) : a + 1 > a := by
  slim_check (config := {quiet := true})

/-- error: Found a counter-example! -/
#guard_msgs in
example (a : BitVec n) : a + 1 > a := by
  slim_check (config := {quiet := true})

/-- error: Found a counter-example! -/
#guard_msgs in
example (a : UInt8) : a - 1 < a := by
  slim_check (config := {quiet := true})

/-- error: Found a counter-example! -/
#guard_msgs in
example (a : UInt16) : a - 1 < a := by
  slim_check (config := {quiet := true})

/-- error: Found a counter-example! -/
#guard_msgs in
example (a : UInt32) : a - 1 < a := by
  slim_check (config := {quiet := true})

/-- error: Found a counter-example! -/
#guard_msgs in
example (a : UInt64) : a - 1 < a := by
  slim_check (config := {quiet := true})

/-- error: Found a counter-example! -/
#guard_msgs in
example (a : USize) : a - 1 < a := by
  slim_check (config := {quiet := true})

/-- error: Found a counter-example! -/
#guard_msgs in
example (a : Char) : a ≠ a := by
  slim_check (config := {quiet := true})

/-- error: Found a counter-example! -/
#guard_msgs in
example (a : Option Char) : a ≠ a := by
  slim_check (config := {quiet := true})

/-- error: Found a counter-example! -/
#guard_msgs in
example (xs ys : List Nat) : xs.length = ys.length → xs = ys := by
  slim_check (config := {quiet := true})

/-- error: Found a counter-example! -/
#guard_msgs in
example (xs ys : String) : xs.length = ys.length → xs = ys := by
  slim_check (config := {quiet := true})

/-- error: Found a counter-example! -/
#guard_msgs in
example (xs ys : Array Nat) : xs.size = ys.size → xs = ys := by
  slim_check (config := {quiet := true})

/-- error: Found a counter-example! -/
#guard_msgs in
example (xs : List Int) (f : Int → Int) : xs.map f = xs := by
  slim_check (config := {quiet := true})

/--
info: Unable to find a counter-example
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example (a : Sum Nat Nat) : a = a := by
  slim_check

/--
warning: Gave up after failing to generate values that fulfill the preconditions 100 times.
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example (a b : Sum Nat Nat) : a ≠ a → a = b := by
  slim_check (config := {numInst := 100})
