import Mathlib.Data.Fintype.Basic

namespace Extensional

  structure TermExtensions where
    XObject           : Type
    XVariable         : Type
    XFuncApplication  : Type
    XOtherTerm        : Type

  structure FormulaExtensions where
    XPredApplication  : Type
    XEquality         : Type
    XNegation         : Type
    XAnd              : Type
    XQuantification   : Type
    XOtherFormula     : Type

  structure Extensions where
    TermExtensions    : TermExtensions
    FormulaExtensions : FormulaExtensions

-- Ungodly coercion rules that will most likely destroy the universe and all efficiency of the Lean 4 system, but they make
-- writing formulas nicer :3
  instance {α: Type} {β}: Coe α (α ⊕ β) where
    coe := Sum.inl

  instance {α: Type} {β: Type}: Coe β (α ⊕ β) where
    coe := Sum.inr

  instance {α: Type}: Coe α (Unit × α) where
    coe := (Prod.mk () ·)

  instance {α β: Type}: Coe (β × α) (α × β) where
    coe := Prod.swap


  structure Domain where
    -- Ideally a Domain would be modelled as disjunct union of a list of types, but I don't know how to do this
    -- Even more, this is only the case when the Types extension is used, if it isn't the domain is in fact of a single type
    -- so uh... do we parametrize this somehow? Or make it a disjunct union of only a single type when the extension is used
    -- and pinky promise to never use a multi-typed domain unless the types extension is used (yikes)
    Types: Type
    Fintype: Fintype Types
    DecidableEq: DecidableEq Types

  structure Context where
    Domain: Domain
    Extensions : Extensions
    -- PropVars: Type

  inductive TermX {ctx : Context} where
  -- Save me lord how can I name these things locally so as not to need the entire hierarchy
  | Object (ext : ctx.Extensions.TermExtensions.XObject) (name : String)
  | Variable (ext : ctx.Extensions.TermExtensions.XVariable) (name : String)
  | FuncApplication (ext : ctx.Extensions.TermExtensions.XFuncApplication) (name : String) (arguments : List (TermX (ctx := ctx)))
  -- AAAAAAAAH these constructors don't have access to the ctx variable, but this is necessary probably
  | Other (ext :ctx.Extensions.TermExtensions.XOtherTerm)

  instance (ctx : Context) : Coe ctx.Extensions.TermExtensions.XOtherTerm (TermX (ctx := ctx)) where
    coe := TermX.Other


  inductive FormulaX {ctx: Context} where
  | PredApplication (ext : ctx.Extensions.FormulaExtensions.XPredApplication) (name : String) (arguments : List (TermX (ctx := ctx)))
  | Equality (ext : ctx.Extensions.FormulaExtensions.XEquality) (t₁ t₂ : TermX (ctx := ctx))
  | Negation (ext : ctx.Extensions.FormulaExtensions.XNegation) (φ : FormulaX (ctx := ctx))
  | And (ext : ctx.Extensions.FormulaExtensions.XAnd) (φ₁ φ₂ : FormulaX (ctx := ctx))
  | Quantification (ext : ctx.Extensions.FormulaExtensions.XQuantification) (name : String) (φ : FormulaX (ctx := ctx))
  | Other (ext : ctx.Extensions.FormulaExtensions.XOtherFormula)

  instance (ctx : Context) : Coe ctx.Extensions.FormulaExtensions.XOtherFormula (FormulaX (ctx := ctx)) where
    coe := FormulaX.Other

end Extensional

namespace FO
  open Extensional

  abbrev PlainFOTerms : TermExtensions :=
  { XObject           := Unit
  , XVariable         := Unit
  , XFuncApplication  := Unit
  , XOtherTerm        := Empty
  }

  abbrev PlainFOFormulas : FormulaExtensions :=
  { XPredApplication  := Unit
  , XEquality         := Unit
  , XNegation         := Unit
  , XAnd              := Unit
  , XQuantification   := Unit
  , XOtherFormula     := Empty
  }

  abbrev PlainFO : Extensions :=
  { TermExtensions := PlainFOTerms
  , FormulaExtensions := PlainFOFormulas
  }

end FO
