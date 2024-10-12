/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Arthur Adjedj
-/

namespace SlimCheck

def Rel (A : Type u) (B : Type v) := (A → B) × (B → A)

def Rel.symm (x : Rel A B) : Rel B A := ⟨x.2,x.1⟩
/-- Given a universe polymorphic type family `M.{u} : Type u₁ → Type
u₂`, this class convert between instantiations, from
`M.{u} : Type u₁ → Type u₂` to `M.{v} : Type v₁ → Type v₂` and back.

`f` is an outParam, because `g` can almost always be inferred from the current monad.
At any rate, the lift should be unique, as the intent is to only lift the same constants with
different universe parameters. -/
class ULiftable (f : outParam (Type u₀ → Type u₁)) (g : Type v₀ → Type v₁) where
  congr : Rel a b → Rel (f a) (g b)

namespace ULiftable

/-- Not an instance as it is incompatible with `outParam`. In practice it seems not to be needed
anyway. -/
abbrev symm (f : Type u₀ → Type u₁) (g : Type v₀ → Type v₁) [ULiftable f g] : ULiftable g f where
  congr e := (ULiftable.congr e.symm).symm

instance refl (f : Type u₀ → Type u₁) [Functor f] : ULiftable f f where
  congr e := ⟨(Functor.map e.1 ·), (Functor.map e.2 ·)⟩

/-- The most common practical use `ULiftable` (together with `down`), the function `up.{v}` takes
`x : M.{u} α` and lifts it to `M.{max u v} (ULift.{v} α)` -/
abbrev up {f : Type u₀ → Type u₁} {g : Type max u₀ v → Type v₁} [h : ULiftable f g] {α} :
    f α → g (ULift.{v} α) :=
  (h.congr ⟨ULift.up,ULift.down⟩).1

end ULiftable

end SlimCheck
