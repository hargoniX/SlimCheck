/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Arthur Adjedj
-/

namespace SlimCheck

def Rel (A : Type u) (B : Type v) := (A → B) × (B → A)

def Rel.refl : Rel A A := ⟨id,id⟩
def Rel.trans (r₁ : Rel A B) (r₂ : Rel B C) : Rel A C := ⟨r₂.1 ∘ r₁.1 ,r₁.2 ∘ r₂.2⟩
def Rel.symm (x : Rel A B) : Rel B A := ⟨x.2,x.1⟩

def Rel.ulift : Rel α (ULift α) := ⟨ULift.up,ULift.down⟩
def Rel.ulift' : Rel (ULift α) α := ⟨ULift.down,ULift.up⟩

def Rel.prod_congr (r₁ : Rel A₁ A₂) (r₂ : Rel B₁ B₂) : Rel (A₁ × B₁) (A₂ × B₂) :=
  ⟨fun e => (⟨r₁.1 e.1,r₂.1 e.2⟩), fun e => ⟨r₁.2 e.1,r₂.2 e.2⟩⟩

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
abbrev up {f : Type u₀ → Type u₁} {g : Type max u₀ v → Type v₁} [self : ULiftable f g] {α} :
    f α → g (ULift.{v} α) :=
  (self.congr Rel.ulift).1

instance instULiftableId : ULiftable Id Id where
  congr F := F

/-- for specific state types, this function helps to create a uliftable instance -/
def StateT.uliftable' {m : Type u₀ → Type v₀} {m' : Type u₁ → Type v₁} [self: ULiftable m m']
    (F : Rel s s') : ULiftable (StateT s m) (StateT s' m') where
  congr := by
    intro α β G
    constructor <;> intro x st
    · exact (self.congr (Rel.prod_congr G F)).1 (x (F.2 st))
    · exact (self.congr (Rel.prod_congr G F)).2 (x (F.1 st))

instance {m m'} [ULiftable m m'] : ULiftable (StateT s m) (StateT (ULift s) m') :=
  StateT.uliftable' Rel.ulift

instance StateT.instULiftableULiftULift {m m'} [ULiftable m m'] :
    ULiftable (StateT (ULift.{max v₀ u₀} s) m) (StateT (ULift.{max v₁ u₀} s) m') :=
  StateT.uliftable' $ Rel.ulift.symm.trans Rel.ulift

/-- for specific reader monads, this function helps to create a uliftable instance -/
def ReaderT.uliftable' {m m'} [self: ULiftable m m'] (F : Rel s s') :
    ULiftable (ReaderT s m) (ReaderT s' m') where
  congr := by
    intro α β G
    constructor <;> intro x st
    · exact (self.congr G).1 (x (F.2 st))
    · exact (self.congr G).2 (x (F.1 st))

instance {m m'} [ULiftable m m'] : ULiftable (ReaderT s m) (ReaderT (ULift s) m') :=
  ReaderT.uliftable' Rel.ulift

instance ReaderT.instULiftableULiftULift {m m'} [ULiftable m m'] :
    ULiftable (ReaderT (ULift.{max v₀ u₀} s) m) (ReaderT (ULift.{max v₁ u₀} s) m') :=
  ReaderT.uliftable' $ Rel.ulift.symm.trans Rel.ulift

end ULiftable

end SlimCheck
