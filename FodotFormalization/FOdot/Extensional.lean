import Mathlib.Data.Fintype.Basic

namespace Extensional

  structure Domain where
    -- Ideally a Domain would be modelled as disjunct union of a list of types, but I don't know how to do this
    -- Even more, this is only the case when the Types extension is used, if it isn't the domain is in fact of a single type
    -- so uh... do we parametrize this somehow? Or make it a disjunct union of only a single type when the extension is used
    -- and pinky promise to never use a multi-typed domain unless the types extension is used (yikes)
    Types: Type
    -- What if below fields are actually decided by another Extension struct, so finite domains is an extension,
    -- DecidableEq domains are an extension (that would then depend on finiteness)?
    -- Might be a little too insane though, there's already way too much extension structs and fields, but... what if more :3
    Fintype: Fintype Types
    DecidableEq: DecidableEq Types


  structure SymbolDeclarationExtensions where
    XPredicate  : Type
    XFunction   : Type
    XOther      : Type

  structure VocabularyExtensions where
    SymbolDeclarationExtensions : SymbolDeclarationExtensions

  inductive SymbolDeclarationX (exts : SymbolDeclarationExtensions) where
  | Predicate (ext : exts.XPredicate) (name : String) (arity : Nat)
  | Function  (ext : exts.XFunction)  (name : String) (arity : Nat)
  | Other     (ext : exts.XOther)

  instance (exts : SymbolDeclarationExtensions) : Coe (exts.XOther) (SymbolDeclarationX exts) where
    coe := SymbolDeclarationX.Other

  structure Vocabulary (exts : VocabularyExtensions) where
    Domain : Domain
    SymbolDeclarations  : Finset (SymbolDeclarationX exts.SymbolDeclarationExtensions)

  structure TermExtensions (exts : VocabularyExtensions) where
    XObject           : Type
    XVariable         : Type
    XFuncApplication  : Type
    XOtherTerm        : Vocabulary exts → Type

  structure FormulaExtensions (exts : VocabularyExtensions) where
    XPredApplication  : Type
    XEquality         : Type
    XNegation         : Type
    XAnd              : Type
    XQuantification   : Type
    XOtherFormula     : Vocabulary exts → Type

  structure Extensions (exts : VocabularyExtensions) where
    TermExtensions    : TermExtensions exts
    FormulaExtensions : FormulaExtensions exts

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

  structure Context where
    VocabularyExtensions  : VocabularyExtensions
    Vocabulary            : Vocabulary VocabularyExtensions
    Extensions            : Extensions VocabularyExtensions

  inductive TermX {vocExts : VocabularyExtensions} (voc : Vocabulary vocExts) (exts : TermExtensions vocExts) where
  -- Save me lord how can I name these things locally so as not to need the entire hierarchy
  | Object (ext : exts.XObject) (name : String)
  | Variable (ext : exts.XVariable) (name : String)
  | FuncApplication (ext : exts.XFuncApplication) (name : String) (arguments : List (TermX voc exts))
  | Other (ext :exts.XOtherTerm voc)

  instance (ctx : Context) : Coe (ctx.Extensions.TermExtensions.XOtherTerm ctx.Vocabulary) (TermX (voc := ctx.Vocabulary) (exts := ctx.Extensions.TermExtensions)) where
    coe := TermX.Other


  inductive FormulaX {vocExts : VocabularyExtensions} (voc : Vocabulary vocExts) (exts : Extensions vocExts) where
  | PredApplication (ext : exts.FormulaExtensions.XPredApplication) (name : String) (arguments : List (TermX voc exts.TermExtensions))
  | Equality (ext : exts.FormulaExtensions.XEquality) (t₁ t₂ : TermX voc exts.TermExtensions)
  | Negation (ext : exts.FormulaExtensions.XNegation) (φ : FormulaX voc exts)
  | And (ext : exts.FormulaExtensions.XAnd) (φ₁ φ₂ : FormulaX voc exts)
  | Quantification (ext : exts.FormulaExtensions.XQuantification) (name : String) (φ : FormulaX voc exts)
  | Other (ext : exts.FormulaExtensions.XOtherFormula voc)

  instance (ctx : Context) : Coe (ctx.Extensions.FormulaExtensions.XOtherFormula ctx.Vocabulary) (FormulaX (voc := ctx.Vocabulary) (exts := ctx.Extensions)) where
    coe := FormulaX.Other

end Extensional
