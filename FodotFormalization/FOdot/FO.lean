import FodotFormalization.FOdot.Extensional

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
