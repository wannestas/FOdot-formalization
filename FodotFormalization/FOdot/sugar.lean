import FodotFormalization.FOdot.Extensional
import FodotFormalization.FOdot.FO

namespace FOsugar
  open Extensional

  abbrev SugarFOTerms (base: Extensions) : TermExtensions :=
  { XObject           := base.TermExtensions.XObject
  , XVariable         := base.TermExtensions.XVariable
  , XFuncApplication  := base.TermExtensions.XFuncApplication
  , XOtherTerm        := base.TermExtensions.XOtherTerm
  }

  inductive SugarFormulas {ctx: Context} where
  | Or (φ₁ φ₂ : FormulaX (ctx := ctx))

  abbrev SugarFOFormulas (base: Extensions) : FormulaExtensions :=
  { XPredApplication  := base.FormulaExtensions.XPredApplication
  , XEquality         := base.FormulaExtensions.XEquality
  , XNegation         := base.FormulaExtensions.XNegation
  , XAnd              := base.FormulaExtensions.XAnd
  , XQuantification   := base.FormulaExtensions.XQuantification
  , XOtherFormula     := SugarFormulas ⊕ base.FormulaExtensions.XOtherFormula
  }

end FOsugar
