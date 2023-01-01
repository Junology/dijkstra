/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Dijkstra.Control.Functor.Subreg
import Dijkstra.Control.Monad.Hom
import Dijkstra.Control.Monad.Spec
import Dijkstra.Control.Monad.Reify

/-!
# Dijkstra wrap over WPPure

As seen in [Dijkstra.Control.Subreg](Dijkstra/Control/Subreg.lean), every monad `m : Type u → Type v` gives rise to a predicate transformer

```lean
def liftWPPure {α : Type u} (x : m α) : (α → Prop) → Prop :=
  λ (z : m (Subtype p)), Subtype.val <$> z = x
```

It turns out that `liftWPPure` actually defines `m α → WPPure α`, and this suggests that we should consider wrapping a computation `m α` with a Dijkstra monad over WPPure.
Indeed, we define the following:

```lean
structure WrapDM (m : Type u → Type v) (α : Type u) (wa : WPPure α) where
  val : m α
  assure : mrel (liftWPPure val) wa
```

We show that `WrapDM m` is a Dijkstra monad over `WPPure` provided the underlying functor of `m` is subregular;see [Dijkstra.Control.Subreg](Dijkstra/Control/Functor/Subreg.lean) for the definition and instances.
Furthermore, in this case, `WrapDM m` also admits a reification in the original monad `m`.
Thus, `WrapDM` can be used to write a specification that ensures a computation result to satisfy a specific property.

-/

universe u v w

def liftWPPure {m : Type u → Type v} [Monad m] [LawfulMonad m] {α : Type u} (x : m α) : WPPure α where
  predT p := mapProp p x
  monotonic hpq hp := by
    cases hp with | intro z hz =>
    cases hz
    exists (λ a => ⟨a.val, hpq a.val a.property⟩) <$> z
    rw [←comp_map]
    rfl

structure WrapDM (m : Type u → Type v) [Monad m] [LawfulMonad m] (α : Type u) (wa : WPPure α) : Type v where
  val : m α
  assure : mrel (liftWPPure val) wa

namespace WrapDM

variable {m : Type u → Type v} [Monad m] [LawfulMonad m]

protected
def eq {α : Type u} {wa : WPPure α} : ∀ {x y : WrapDM m α wa}, x.val = y.val → x = y
| mk _ _, mk _ _, rfl => rfl

protected
def deq {α : Type u} : ∀ {wa wb : WPPure α} {x : WrapDM m α wa} {y : WrapDM m α wb}, wa = wb → x.val = y.val → DEq (WrapDM m α) x y
| _, _, mk _ _, mk _ _, rfl, rfl => DEq.refl _

def weaken {α : Type u} {wa wb : WPPure α} : mrel wa wb → WrapDM m α wa → WrapDM m α wb :=
  λ h x => {val := x.val, assure := λ p hp => x.assure p (h p hp)}

def wrapDM {α : Type u} (x : m α) : WrapDM m α (liftWPPure x) where
  val := x
  assure _ := id

instance instDijkstraMonadWrapDM [SubregFunctor m] : DijkstraMonad WPPure (WrapDM m) where
  dpure a := {
    val := pure a
    assure :=
      λ p hp => Exists.intro (pure ⟨a,hp⟩) (by rw [map_pure])
  }
  dbind x f := {
    val := x.val >>= (λ a => (f a).val)
    assure := by
      dsimp [bind]
      intro p wpp
      exists do
        let za ← SubregFunctor.ensureF x.val (x.assure _ wpp)
        SubregFunctor.ensureF (f za.val).val ((f za.val).assure p za.property)
      conv =>
        lhs; rw [map_eq_pure_bind, bind_assoc]
        rhs; ext a; rw [←map_eq_pure_bind, SubregFunctor.val_ensureF]
        change ((λ a => (f a).val) ∘ Subtype.val) a
      rw [←map_bind, SubregFunctor.val_ensureF]
  }

instance instDijkstraMonadLawfulWrapDM [SubregFunctor m] : DijkstraMonad.Lawful WPPure (WrapDM m) where
  dbind_dpure := by
    intros; exact WrapDM.deq (bind_pure (m:=WPPure) _) (bind_pure (m:=m) _)
  dpure_dbind := by
    intros; exact WrapDM.deq (pure_bind (m:=WPPure) _ _) (pure_bind (m:=m) _ _)
  dbind_assoc := by
    intros; exact WrapDM.deq (bind_assoc (m:=WPPure) _ _ _) (bind_assoc (m:=m) _ _ _)

instance instReificationWrapDM [SubregFunctor m] : Reification WPPure.validate (WrapDM m) m where 
  dLift h x := SubregFunctor.ensureF x.val (x.assure _ h)

instance instReificationLawfulWrapDM [SubregFunctor m] : Reification.Lawful WPPure.validate (WrapDM m) m where
  dLift_dpure a := by
    dsimp [DijkstraLift.dLift, dpure, pure]
    apply SubregFunctor.val_inj
    rw [SubregFunctor.val_ensureF, map_pure]
  dLift_dbind {α β} {wa wf pa pf ha hf} x f := by
    dsimp [DijkstraLift.dLift, dbind, bind]
    apply SubregFunctor.val_inj
    conv => lhs; rw [SubregFunctor.val_ensureF]
    conv =>
      rhs; rw [map_eq_pure_bind, bind_assoc]
      rhs; ext z; rw [bind_assoc]
      rhs; ext zb; rw [pure_bind]; dsimp
    conv =>
      rhs; rhs; ext; rw [←map_eq_pure_bind]; rw [SubregFunctor.val_ensureF]
    conv =>
      rhs; rhs; change (λ a => (f a).val) ∘ Subtype.val (p:=pa)
    conv =>
      rhs; rw [←map_bind]; rw [SubregFunctor.val_ensureF]
  reify_weaken {_} {wa} {p q} hpq x hp := by
    dsimp [reify, DijkstraLift.dLift, SubtypeT.weaken]
    apply SubregFunctor.val_inj
    conv =>
      rhs; rw [SubregFunctor.val_ensureF]
    conv =>
      lhs; rw [map_eq_pure_bind, bind_assoc]
      rhs; ext; rw [pure_bind]; dsimp
    rw [←map_eq_pure_bind, SubregFunctor.val_ensureF]

end WrapDM

export WrapDM (wrapDM)
