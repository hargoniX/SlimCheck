/-
Copyright (c) 2022 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving, Simon Hudon
-/
import Lean.Elab.Command
import SlimCheck.Gen

/-!
# `SampleableExt` Class

This class permits the creation samples of a given type
controlling the size of those values using the `Gen` monad.

# `Shrinkable` Class

This class helps minimize examples by creating smaller versions of
given values.

When testing a proposition like `∀ n : ℕ, Prime n → n ≤ 100`,
`SlimCheck` requires that `ℕ` have an instance of `SampleableExt` and for
`Prime n` to be decidable.  `SlimCheck` will then use the instance of
`SampleableExt` to generate small examples of ℕ and progressively increase
in size. For each example `n`, `Prime n` is tested. If it is false,
the example will be rejected (not a test success nor a failure) and
`SlimCheck` will move on to other examples. If `Prime n` is true,
`n ≤ 100` will be tested. If it is false, `n` is a counter-example of
`∀ n : ℕ, Prime n → n ≤ 100` and the test fails. If `n ≤ 100` is true,
the test passes and `SlimCheck` moves on to trying more examples.

This is a port of the Haskell QuickCheck library.

## Main definitions

* `SampleableExt` class
* `Shrinkable` class

### `SampleableExt`

`SampleableExt` can be used in two ways. The first (and most common)
is to simply generate values of a type directly using the `Gen` monad,
if this is what you want to do then `SampleableExt.mkSelfContained` is
the way to go.

Furthermore it makes it possible to express generators for types that
do not lend themselves to introspection, such as `ℕ → ℕ`.
If we test a quantification over functions the
counter-examples cannot be shrunken or printed meaningfully.
For that purpose, `SampleableExt` provides a proxy representation
`proxy` that can be printed and shrunken as well
as interpreted (using `interp`) as an object of the right type. If you
are using it in the first way, this proxy type will simply be the type
itself and the `interp` function `id`.

### `Shrinkable`

Given an example `x : α`, `Shrinkable α` gives us a way to shrink it
and suggest simpler examples.

## Shrinking

Shrinking happens when `SlimCheck` find a counter-example to a
property.  It is likely that the example will be more complicated than
necessary so `SlimCheck` proceeds to shrink it as much as
possible. Although equally valid, a smaller counter-example is easier
for a user to understand and use.

The `Shrinkable` class, , has a `shrink` function so that we can use
specialized knowledge while shrinking a value. It is not responsible
for the whole shrinking process however. It only has to take one step
in the shrinking process. `SlimCheck` will repeatedly call `shrink`
until no more steps can be taken. Because `shrink` guarantees that the
size of the candidates it produces is strictly smaller than the
argument, we know that `SlimCheck` is guaranteed to terminate.

## Tags

random testing

## References

* https://hackage.haskell.org/package/QuickCheck

-/

namespace SlimCheck

open Random Gen

universe u v
variable {α β : Type _}

/-- Given an example `x : α`, `Shrinkable α` gives us a way to shrink it
and suggest simpler examples. -/
class Shrinkable (α : Type u) where
  shrink : (x : α) → List α := fun _ ↦ []

/-- `SampleableExt` can be used in two ways. The first (and most common)
is to simply generate values of a type directly using the `Gen` monad,
if this is what you want to do then `SampleableExt.mkSelfContained` is
the way to go.

Furthermore it makes it possible to express generators for types that
do not lend themselves to introspection, such as `ℕ → ℕ`.
If we test a quantification over functions the
counter-examples cannot be shrunken or printed meaningfully.
For that purpose, `SampleableExt` provides a proxy representation
`proxy` that can be printed and shrunken as well
as interpreted (using `interp`) as an object of the right type. -/
class SampleableExt (α : Sort u) where
  proxy : Type v
  [proxyRepr : Repr proxy]
  [shrink : Shrinkable proxy]
  sample : Gen proxy
  interp : proxy → α

attribute [instance] SampleableExt.proxyRepr
attribute [instance] SampleableExt.shrink

namespace SampleableExt

/-- Use to generate instance whose purpose is to simply generate values
of a type directly using the `Gen` monad -/
def mkSelfContained [Repr α] [Shrinkable α] (sample : Gen α) : SampleableExt α where
  proxy := α
  proxyRepr := inferInstance
  shrink := inferInstance
  sample := sample
  interp := id

/-- First samples a proxy value and interprets it. Especially useful if
the proxy and target type are the same. -/
def interpSample (α : Type u) [SampleableExt α] : Gen α :=
  SampleableExt.interp <$> SampleableExt.sample

end SampleableExt

section Shrinkers

/-- `Nat.shrink' n` creates a list of smaller natural numbers by
successively dividing `n` by 2 . For example, `Nat.shrink 5 = [2, 1, 0]`. -/
def Nat.shrink (n : Nat) : List Nat :=
  if h : 0 < n then
    let m := n/2
    m :: shrink m
  else
    []

instance Nat.shrinkable : Shrinkable Nat where
  shrink := Nat.shrink

instance Fin.shrinkable {n : Nat} : Shrinkable (Fin n.succ) where
  shrink m := Nat.shrink m |>.map Fin.ofNat

/-- `Int.shrinkable` operates like `Nat.shrinkable` but also includes the negative variants. -/
instance Int.shrinkable : Shrinkable Int where
  shrink n :=
    let converter n :=
      let int := Int.ofNat n
      [int, -int]
    Nat.shrink n.natAbs |>.bind converter

instance Bool.shrinkable : Shrinkable Bool := {}
instance Char.shrinkable : Shrinkable Char := {}

instance Prod.shrinkable [shrA : Shrinkable α] [shrB : Shrinkable β] :
    Shrinkable (Prod α β) where
  shrink := fun (fst,snd) ↦
    let shrink1 := shrA.shrink fst |>.map fun x ↦ (x, snd)
    let shrink2 := shrB.shrink snd |>.map fun x ↦ (fst, x)
    shrink1 ++ shrink2

instance Sigma.shrinkable [shrA : Shrinkable α] [shrB : Shrinkable β] :
    Shrinkable ((_ : α) × β) where
  shrink := fun ⟨fst,snd⟩ ↦
    let shrink1 := shrA.shrink fst |>.map fun x ↦ ⟨x, snd⟩
    let shrink2 := shrB.shrink snd |>.map fun x ↦ ⟨fst, x⟩
    shrink1 ++ shrink2

open Shrinkable

/-- Shrink a list of a shrinkable type, either by discarding an element or shrinking an element. -/
instance List.shrinkable [Shrinkable α] : Shrinkable (List α) where
  shrink := fun L =>
    (L.mapIdx fun i _ => L.eraseIdx i) ++
    (L.mapIdx fun i a => (shrink a).map fun a' => L.modifyNth (fun _ => a') i).join

end Shrinkers

section Samplers

open SampleableExt

instance Nat.sampleableExt : SampleableExt Nat :=
  mkSelfContained (do choose Nat 0 (← getSize) (Nat.zero_le _))

instance Fin.sampleableExt {n : Nat} : SampleableExt (Fin (n.succ)) :=
  mkSelfContained (do choose (Fin n.succ) (Fin.ofNat 0) (Fin.ofNat (← getSize)) (by
    simp only [Fin.ofNat, Fin.val_zero]
    exact Nat.zero_le _))

instance Int.sampleableExt : SampleableExt Int :=
  mkSelfContained do
    choose Int (-(← getSize)) (← getSize) (by omega)

instance Bool.sampleableExt : SampleableExt Bool :=
  mkSelfContained <| chooseAny Bool

/-- This can be specialized into customized `SampleableExt Char` instances.
The resulting instance has `1 / length` chances of making an unrestricted choice of characters
and it otherwise chooses a character from `chars` with uniform probabilities. -/
def Char.sampleable (length : Nat) (chars : List Char) (pos : 0 < chars.length) :
    SampleableExt Char :=
  mkSelfContained do
    let x ← choose Nat 0 length (Nat.zero_le _)
    if x.val == 0 then
      let n ← interpSample Nat
      pure <| Char.ofNat n
    else
      elements chars pos

instance Char.sampleableDefault : SampleableExt Char :=
  Char.sampleable 3 " 0123abcABC:,;`\\/".toList (by decide)

instance Prod.sampleableExt {α : Type u} {β : Type v} [SampleableExt α] [SampleableExt β] :
    SampleableExt (α × β) where
  proxy := Prod (proxy α) (proxy β)
  proxyRepr := inferInstance
  shrink := inferInstance
  sample := prodOf sample sample
  interp := Prod.map interp interp

instance Prop.sampleableExt : SampleableExt Prop where
  proxy := Bool
  proxyRepr := inferInstance
  sample := interpSample Bool
  shrink := inferInstance
  interp := Coe.coe

instance List.sampleableExt [SampleableExt α] : SampleableExt (List α) where
  proxy := List (proxy α)
  sample := Gen.listOf sample
  interp := List.map interp

end Samplers

/-- An annotation for values that should never get shrunk. -/
def NoShrink (α : Type u) := α

namespace NoShrink

def mk (x : α) : NoShrink α := x
def get (x : NoShrink α) : α := x

instance inhabited [inst : Inhabited α] : Inhabited (NoShrink α) := inst
instance repr [inst : Repr α] : Repr (NoShrink α) := inst

instance shrinkable : Shrinkable (NoShrink α) where
  shrink := fun _ ↦ []

instance sampleableExt [SampleableExt α] [Repr α] : SampleableExt (NoShrink α) :=
  SampleableExt.mkSelfContained <| (NoShrink.mk ∘ SampleableExt.interp) <$> SampleableExt.sample

end NoShrink


/--
Print (at most) 10 samples of a given type to stdout for debugging.
-/
def printSamples {t : Type} [Repr t] (g : Gen t) : IO PUnit := do
  for i in List.range 10 do
    IO.println s!"{repr (← g.run i)}"

open Lean Meta Elab

/-
open Lean Meta
/-- Create a `Gen α` expression from the argument of `#sample` -/
def mkGenerator (e : Expr) : MetaM (Σ (u : Level) (α : Q(Type $u)), Q(Repr $α) × Q(Gen $α)) := do
  match ← inferTypeQ e with
  | ⟨.succ u, ~q(Gen $α), gen⟩ =>
    let repr_inst ← synthInstanceQ (q(Repr $α) : Q(Type $u))
    pure ⟨u, α, repr_inst, gen⟩
  | ⟨.succ u, ~q(Sort u), α⟩ => do
    let v ← mkFreshLevelMVar
    let _sampleableExt_inst ← synthInstanceQ (q(SampleableExt.{u,v} $α) : Q(Sort (max u (v + 2))))
    let v ← instantiateLevelMVars v
    let repr_inst := q(SampleableExt.proxyRepr (α := $α))
    let gen := q(SampleableExt.sample (α := $α))
    pure ⟨v, q(SampleableExt.proxy $α), repr_inst, gen⟩
  | ⟨_u, t, _e⟩ =>
    throwError "Must be a Sort u` or a `Gen α`, got value of type{indentExpr t}"
-/

/--
`e` is a type to sample from, this can either be a type that implements `SampleableExt` or `Gen α`
directly. For this return:
- the universe level of the `Type u` that the relevant type to sample lives in.
- the actual type `α` to sample from
- a `Repr α` instance
- a `Gen α` generator to run in order to sample
-/
private def mkGenerator (e : Expr) : MetaM (Level × Expr × Expr × Expr) := do
  let exprTyp ← inferType e
  let .sort u ← whnf (← inferType exprTyp) | throwError m!"{exprTyp} is not a type"
  let .succ u := u | throwError m!"{exprTyp} is not a type with computational content"
  match_expr exprTyp with
  | Gen α =>
    let reprInst ← synthInstance (mkApp (mkConst ``Repr [u]) α)
    return ⟨u, α, reprInst, e⟩
  | _ =>
    let v ← mkFreshLevelMVar
    let sampleableExtInst ← synthInstance (mkApp (mkConst ``SampleableExt [u, v]) e)
    let v ← instantiateLevelMVars v
    let reprInst := mkApp2 (mkConst ``SampleableExt.proxyRepr [u, v]) e sampleableExtInst
    let gen := mkApp2 (mkConst ``SampleableExt.sample [u, v]) e sampleableExtInst
    let typ := mkApp2 (mkConst ``SampleableExt.proxy [u, v]) e sampleableExtInst
    return ⟨v, typ, reprInst, gen⟩

/--
`#sample type`, where `type` has an instance of `SampleableExt`, prints ten random
values of type `type` using an increasing size parameter.

```lean
#sample Nat
-- prints
-- 0
-- 0
-- 2
-- 24
-- 64
-- 76
-- 5
-- 132
-- 8
-- 449
-- or some other sequence of numbers

#sample List Int
-- prints
-- []
-- [1, 1]
-- [-7, 9, -6]
-- [36]
-- [-500, 105, 260]
-- [-290]
-- [17, 156]
-- [-2364, -7599, 661, -2411, -3576, 5517, -3823, -968]
-- [-643]
-- [11892, 16329, -15095, -15461]
-- or whatever
```
-/
elab "#sample " e:term : command =>
  Command.runTermElabM fun _ => do
    let e ← Elab.Term.elabTermAndSynthesize e none
    let g ← mkGenerator e
    let ⟨0, α, repr, gen⟩ := g | throwError "Cannot sample from {g.1} due to its universe"
    let printSamples := mkApp3 (mkConst ``printSamples) α repr gen
    let code ← unsafe evalExpr (IO PUnit) (mkApp (mkConst ``IO) (mkConst ``PUnit [1])) printSamples
    _ ← code

end SlimCheck
