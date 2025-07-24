import FodotFormalization.FOdot.Extensional

namespace FO
  open Extensional

  abbrev PlainFOSymbolDeclarations : SymbolDeclarationExtensions :=
  { XPredicate  := Unit
  , XFunction   := Unit
  , XOther      := Empty
  }

  abbrev PlainFOVoc : VocabularyExtensions :=
  { SymbolDeclarationExtensions := PlainFOSymbolDeclarations
  }

  abbrev PlainFOTerms : TermExtensions PlainFOVoc :=
  { XObject           := Unit
  , XVariable         := Unit
  , XFuncApplication  := Unit
  , XOtherTerm        := λ _ => Empty
  }

  abbrev PlainFOFormulas : FormulaExtensions PlainFOVoc :=
  { XPredApplication  := Unit
  , XEquality         := Unit
  , XNegation         := Unit
  , XAnd              := Unit
  , XQuantification   := Unit
  , XOtherFormula     := λ _ => Empty
  }

  abbrev PlainFO : Extensions PlainFOVoc :=
  { TermExtensions := PlainFOTerms
  , FormulaExtensions := PlainFOFormulas
  }

end FO
